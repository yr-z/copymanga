package top.fumiama.copymanga.view

import android.content.Context
import android.graphics.Bitmap
import android.graphics.Canvas
import android.graphics.Matrix
import android.graphics.Paint
import android.graphics.RectF
import android.os.Handler
import android.os.Looper
import android.util.AttributeSet
import android.util.Log
import android.view.GestureDetector
import android.view.MotionEvent
import android.view.ScaleGestureDetector
import android.view.View
import android.widget.OverScroller
import java.util.Collections
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import kotlin.math.abs
import kotlin.math.max
import kotlin.math.min
import kotlin.math.roundToInt

/**
 * 高性能漫画长图画布视图（移植自 TuXun JmComicLongCanvasView / LocalComicLongCanvasView）
 *
 * 核心特性：
 * 1. 纯 Canvas 统一渲染：彻底取代传统 NestedScrollView/RecyclerView + 多 ImageView 堆叠，消除卡顿与白边。
 * 2. 无缝拼图算法 (PAGE_STITCH_OVERLAP)：微像素级重叠拼接，消灭切片条漫中间的白线与接缝。
 * 3. 动态虚拟布局与平滑重排 (Reflow Anchor)：图片尺寸异步加载就绪后，基于视口锚点自动重流，阅读位置不跳跃。
 * 4. 窗口化内存管理与自动回收：仅保留可视区域及前后缓冲区位图，远端页面自动 recycle，根除多图 OOM。
 * 5. 惯性滚动与多点触控缩放：支持 OverScroller 惯性甩动、双指自由缩放 (1x~5x) 与双击快速放大。
 */
class ComicLongCanvasView @JvmOverloads constructor(
    context: Context,
    attrs: AttributeSet? = null,
    defStyleAttr: Int = 0
) : View(context, attrs, defStyleAttr) {

    fun interface OnPageChangeListener {
        fun onPageChange(currentPage: Int, totalPages: Int)
    }

    fun interface OnLoadingChangeListener {
        fun onLoadingChange(isLoading: Boolean)
    }

    fun interface OnTransformChangeListener {
        fun onTransformChange()
    }

    interface OnEdgeListener {
        fun onReachTop()
        fun onReachBottom()
    }

    fun interface PageBitmapLoader {
        fun loadBitmap(pageIndex: Int, targetWidth: Int): Bitmap?
    }

    companion object {
        private const val TAG = "ComicLongCanvas"
        private const val DEFAULT_ASPECT_RATIO = 1.45f
        private const val MAX_SCALE = 5.0f
        private const val PRELOAD_SCREEN_MULTIPLIER = 1.5f
        private const val KEEP_SCREEN_MULTIPLIER = 3.0f
        private const val KEEP_PAGE_RADIUS = 24
        private const val MAX_VISIBLE_LOADS = 4
        private const val PAGE_STITCH_OVERLAP = 0.75f
    }

    private val bitmapPaint = Paint(Paint.FILTER_BITMAP_FLAG or Paint.DITHER_FLAG)
    private val backgroundPaint = Paint().apply { color = 0xFF000000.toInt() }
    private val placeholderPaint = Paint().apply { color = 0xFF181A20.toInt() }
    private val textPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = 0xFF8A8D96.toInt()
        textSize = 42f
        textAlign = Paint.Align.CENTER
    }
    private val imageMatrix = Matrix()
    private val drawRect = RectF()

    private val scroller = OverScroller(context)
    private val scaleDetector = ScaleGestureDetector(context, ScaleListener())
    private val gestureDetector = GestureDetector(context, GestureListener())
    private val mainHandler = Handler(Looper.getMainLooper())
    private var executor: ExecutorService = Executors.newFixedThreadPool(3)

    private val pageMetrics = ArrayList<PageMetric>()
    private var totalHeight = 0f
    private var currentScale = 1.0f
    private var estimatedAspectRatio = DEFAULT_ASPECT_RATIO
    private var chapterGeneration = 0L
    private var detached = false
    private var lastDispatchedPage = -1

    private var onPageChangeListener: OnPageChangeListener? = null
    private var onLoadingChangeListener: OnLoadingChangeListener? = null
    private var onTransformChangeListener: OnTransformChangeListener? = null
    private var onEdgeListener: OnEdgeListener? = null
    private var bitmapLoader: PageBitmapLoader? = null

    init {
        setBackgroundColor(0xFF000000.toInt())
    }

    fun setOnPageChangeListener(listener: OnPageChangeListener?) {
        onPageChangeListener = listener
    }

    fun setOnLoadingChangeListener(listener: OnLoadingChangeListener?) {
        onLoadingChangeListener = listener
    }

    fun setOnTransformChangeListener(listener: OnTransformChangeListener?) {
        onTransformChangeListener = listener
    }

    fun setOnEdgeListener(listener: OnEdgeListener?) {
        onEdgeListener = listener
    }

    fun setPageBitmapLoader(loader: PageBitmapLoader?) {
        bitmapLoader = loader
    }

    /**
     * 初始化章节页面数
     * @param count 总页数
     * @param initialPage 初始页码 (0-indexed)
     */
    fun setPageCount(count: Int, initialPage: Int = 0) {
        chapterGeneration++
        lastDispatchedPage = -1
        scroller.forceFinished(true)
        recycleAllBitmaps()
        pageMetrics.clear()
        totalHeight = 0f
        currentScale = 1.0f
        estimatedAspectRatio = DEFAULT_ASPECT_RATIO
        imageMatrix.reset()

        if (count <= 0) {
            dispatchLoadingChanged(false)
            dispatchPageChanged()
            invalidate()
            return
        }

        val baseWidth = max(width, 1080)
        val fallbackHeight = max(1, (baseWidth * estimatedAspectRatio).roundToInt())
        for (i in 0 until count) {
            pageMetrics.add(PageMetric(i, baseWidth, fallbackHeight))
        }

        recomputePageOffsets()
        totalHeight = computeTotalHeight()
        applyInitialPosition(initialPage)
        dispatchLoadingChanged(true)
        dispatchPageChanged()
        invalidate()
    }

    /**
     * 重新加载某特定页（例如单页下载完成或重试）
     */
    fun reloadPage(pageIndex: Int) {
        if (pageIndex in pageMetrics.indices) {
            val metric = pageMetrics[pageIndex]
            metric.isFailed = false
            metric.isLoading = false
            metric.retryCount = 0
            metric.bitmap?.recycle()
            metric.bitmap = null
            invalidate()
        }
    }

    fun hasAnyBitmapLoaded(): Boolean {
        for (metric in pageMetrics) {
            if (metric.bitmap != null && !metric.bitmap!!.isRecycled) {
                return true
            }
        }
        return false
    }

    fun findPageAtScreenY(screenY: Float): Int {
        if (pageMetrics.isEmpty() || height <= 0) return -1
        for (index in pageMetrics.indices) {
            val rect = getPageScreenRect(index)
            if (screenY >= rect.top && screenY <= rect.bottom) {
                return index
            }
        }
        return -1
    }

    fun getPageBitmap(pageIndex: Int): Bitmap? {
        if (pageIndex in pageMetrics.indices) {
            val bmp = pageMetrics[pageIndex].bitmap
            if (bmp != null && !bmp.isRecycled) {
                return bmp
            }
        }
        return null
    }

    fun getPageScreenRect(pageIndex: Int): RectF {
        if (pageIndex !in pageMetrics.indices || width <= 0) {
            return RectF()
        }
        val metric = pageMetrics[pageIndex]
        val pageHeight = metric.getDisplayHeight(width)
        val unscaled = RectF(0f, metric.startY, width.toFloat(), metric.startY + pageHeight)
        val screenRect = RectF()
        imageMatrix.mapRect(screenRect, unscaled)
        return screenRect
    }

    fun getTransformMatrix(): Matrix = Matrix(imageMatrix)

    /**
     * 捕获当前可视区域截图
     */
    fun captureVisibleViewportBitmap(): Bitmap? {
        val w = width
        val h = height
        if (w <= 0 || h <= 0 || pageMetrics.isEmpty()) return null
        return try {
            val bitmap = Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888)
            val canvas = Canvas(bitmap)
            canvas.drawRect(0f, 0f, w.toFloat(), h.toFloat(), backgroundPaint)
            canvas.save()
            canvas.concat(imageMatrix)
            for (index in pageMetrics.indices) {
                val metric = pageMetrics[index]
                val pageHeight = metric.getDisplayHeight(w)
                val drawTop = metric.startY - (if (index > 0) PAGE_STITCH_OVERLAP else 0f)
                val drawBottom = metric.startY + pageHeight + (if (index < pageMetrics.size - 1) PAGE_STITCH_OVERLAP else 0f)
                drawRect.set(0f, drawTop, w.toFloat(), drawBottom)
                val bmp = metric.bitmap
                if (bmp != null && !bmp.isRecycled) {
                    canvas.drawBitmap(bmp, null, drawRect, bitmapPaint)
                }
            }
            canvas.restore()
            bitmap
        } catch (e: OutOfMemoryError) {
            Log.e(TAG, "OOM in captureVisibleViewportBitmap", e)
            null
        }
    }

    fun getPageCount(): Int = pageMetrics.size

    /**
     * 获取当前可视面积最大的页面索引 (0-indexed)
     */
    fun getCurrentPageIndex(): Int {
        if (pageMetrics.isEmpty() || height <= 0) return 0
        val viewHeight = height.toFloat()
        var bestIndex = 0
        var maxVisibleH = -1f
        for (index in pageMetrics.indices) {
            val screenRect = getPageScreenRect(index)
            val visibleTop = max(0f, screenRect.top)
            val visibleBottom = min(viewHeight, screenRect.bottom)
            val visibleH = max(0f, visibleBottom - visibleTop)
            if (visibleH > maxVisibleH) {
                maxVisibleH = visibleH
                bestIndex = index
            }
        }
        return bestIndex
    }

    /**
     * 跳转至指定页
     */
    fun scrollToPage(pageIndex: Int, smooth: Boolean = false) {
        if (pageIndex !in pageMetrics.indices) return
        scroller.forceFinished(true)
        val targetY = -pageMetrics[pageIndex].startY * currentScale
        val values = FloatArray(9)
        imageMatrix.getValues(values)
        val startY = values[Matrix.MTRANS_Y]
        if (!smooth) {
            if (abs(startY - targetY) < 1f) return
            imageMatrix.setTranslate(values[Matrix.MTRANS_X], targetY)
            checkTranslationBounds()
            dispatchPageChanged()
            dispatchTransformChanged()
            invalidate()
        } else {
            val startYInt = startY.roundToInt()
            val dy = (targetY - startYInt).roundToInt()
            if (abs(dy) <= 1) return
            scroller.startScroll(0, startYInt, 0, dy, 350)
            postInvalidateOnAnimation()
        }
    }

    /**
     * 相对滚动指定距离（如音量键翻页）
     */
    fun scrollByDistance(distanceY: Float, smooth: Boolean = true) {
        scroller.forceFinished(true)
        if (!smooth) {
            imageMatrix.postTranslate(0f, -distanceY)
            checkTranslationBounds()
            dispatchPageChanged()
            dispatchTransformChanged()
            invalidate()
        } else {
            val values = FloatArray(9)
            imageMatrix.getValues(values)
            val startY = values[Matrix.MTRANS_Y].roundToInt()
            scroller.startScroll(0, startY, 0, (-distanceY).roundToInt(), 250)
            postInvalidateOnAnimation()
        }
    }

    override fun onSizeChanged(w: Int, h: Int, oldw: Int, oldh: Int) {
        super.onSizeChanged(w, h, oldw, oldh)
        if (w <= 0 || h <= 0 || pageMetrics.isEmpty()) return

        val oldOffsetY = getCurrentUnscaledOffsetY()
        val oldTotalHeight = totalHeight
        val anchor = captureViewportAnchor(oldOffsetY)
        recomputePageOffsets()
        totalHeight = computeTotalHeight()
        restoreOffsetAfterReflow(oldOffsetY, oldTotalHeight, totalHeight, anchor)
        checkTranslationBounds()
        dispatchTransformChanged()
        invalidate()
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)

        if (scroller.computeScrollOffset()) {
            val values = FloatArray(9)
            imageMatrix.getValues(values)
            val deltaY = scroller.currY - values[Matrix.MTRANS_Y]
            imageMatrix.postTranslate(0f, deltaY)
            checkTranslationBounds()
            postInvalidateOnAnimation()
            dispatchPageChanged()
            dispatchTransformChanged()
        }

        canvas.drawRect(0f, 0f, width.toFloat(), height.toFloat(), backgroundPaint)
        if (pageMetrics.isEmpty() || width <= 0) return

        scheduleVisibleLoads()

        val viewport = getUnscaledViewport()
        val visibleTop = viewport.top - 100f
        val visibleBottom = viewport.bottom + 100f

        canvas.save()
        canvas.concat(imageMatrix)
        for (index in pageMetrics.indices) {
            val metric = pageMetrics[index]
            val pageHeight = metric.getDisplayHeight(width)
            val pageTop = metric.startY
            val pageBottom = pageTop + pageHeight
            if (pageBottom < visibleTop || pageTop > visibleBottom) {
                continue
            }
            val drawTop = pageTop - (if (index > 0) PAGE_STITCH_OVERLAP else 0f)
            val drawBottom = pageBottom + (if (index < pageMetrics.size - 1) PAGE_STITCH_OVERLAP else 0f)
            drawRect.set(0f, drawTop, width.toFloat(), drawBottom)
            val bmp = metric.bitmap
            if (bmp != null && !bmp.isRecycled) {
                canvas.drawBitmap(bmp, null, drawRect, bitmapPaint)
            } else {
                canvas.drawRect(drawRect, placeholderPaint)
                val text = if (metric.isFailed) {
                    "第 ${index + 1} 页 加载失败 (轻触重试)"
                } else {
                    "第 ${index + 1} 页 加载中..."
                }
                val centerX = width / 2f
                val centerY = drawTop + pageHeight / 2f
                canvas.drawText(text, centerX, centerY, textPaint)
            }
        }
        canvas.restore()
    }

    override fun performClick(): Boolean {
        super.performClick()
        return true
    }

    override fun onTouchEvent(event: MotionEvent): Boolean {
        if (event.actionMasked == MotionEvent.ACTION_DOWN) {
            scroller.forceFinished(true)
        }
        val scaleHandled = scaleDetector.onTouchEvent(event)
        val gestureHandled = gestureDetector.onTouchEvent(event)
        if (event.actionMasked == MotionEvent.ACTION_UP || event.actionMasked == MotionEvent.ACTION_CANCEL) {
            checkTranslationBounds()
            invalidate()
        }
        return scaleHandled || gestureHandled || super.onTouchEvent(event)
    }

    override fun onAttachedToWindow() {
        super.onAttachedToWindow()
        detached = false
        if (executor.isShutdown || executor.isTerminated) {
            executor = Executors.newFixedThreadPool(3)
        }
    }

    override fun onDetachedFromWindow() {
        detached = true
        chapterGeneration++
        lastDispatchedPage = -1
        scroller.forceFinished(true)
        recycleAllBitmaps()
        executor.shutdownNow()
        super.onDetachedFromWindow()
    }

    private fun scheduleVisibleLoads() {
        if (detached || pageMetrics.isEmpty() || width <= 0 || height <= 0) return

        val viewport = getUnscaledViewport()
        recycleFarBitmaps(viewport.top, viewport.bottom)

        val preloadMargin = (height / max(currentScale, 1f)) * PRELOAD_SCREEN_MULTIPLIER
        val loadTop = viewport.top - preloadMargin
        val loadBottom = viewport.bottom + preloadMargin
        val currentPage = getCurrentPageIndex()

        val targets = ArrayList<PageLoadTarget>()
        for (index in pageMetrics.indices) {
            val metric = pageMetrics[index]
            if (metric.bitmap != null || metric.isLoading) continue
            if (metric.isFailed && metric.retryCount >= 2) continue
            val pageBottom = metric.startY + metric.getDisplayHeight(width)
            if (pageBottom > loadTop && metric.startY < loadBottom) {
                targets.add(PageLoadTarget(index, metric))
            }
        }

        if (targets.isEmpty()) {
            maybeDispatchLoadingFinished()
            return
        }

        Collections.sort(targets) { t1, t2 ->
            abs(t1.index - currentPage).compareTo(abs(t2.index - currentPage))
        }

        var loadCount = 0
        for (target in targets) {
            if (loadCount >= MAX_VISIBLE_LOADS) break
            target.metric.isLoading = true
            target.metric.retryCount++
            enqueueBitmapLoad(target.index, target.metric)
            loadCount++
        }
    }

    private fun enqueueBitmapLoad(index: Int, metric: PageMetric) {
        val generation = chapterGeneration
        val targetWidth = max(width, 1080)
        executor.execute {
            val loader = bitmapLoader
            val bitmap = loader?.loadBitmap(metric.pageIndex, targetWidth)
            val result = if (bitmap != null) {
                BitmapLoadResult(bitmap, bitmap.width, bitmap.height)
            } else null
            mainHandler.post {
                applyBitmapLoadResult(generation, index, metric, result)
            }
        }
    }

    private fun applyBitmapLoadResult(
        generation: Long,
        index: Int,
        metric: PageMetric,
        result: BitmapLoadResult?
    ) {
        if (detached || generation != chapterGeneration || index !in pageMetrics.indices || pageMetrics[index] !== metric) {
            metric.isLoading = false
            result?.bitmap?.let { if (!it.isRecycled) it.recycle() }
            return
        }

        metric.isLoading = false
        if (result == null || result.bitmap == null) {
            metric.isFailed = true
            invalidate()
            maybeDispatchLoadingFinished()
            return
        }

        val oldOffsetY = getCurrentUnscaledOffsetY()
        val oldTotalHeight = totalHeight
        val anchor = captureViewportAnchor(oldOffsetY)

        metric.bitmap = result.bitmap
        metric.isFailed = false
        val dimensionChanged = !metric.hasRealDimension ||
                metric.originalWidth != result.originalWidth ||
                metric.originalHeight != result.originalHeight

        if (dimensionChanged) {
            metric.originalWidth = max(1, result.originalWidth)
            metric.originalHeight = max(1, result.originalHeight)
            metric.hasRealDimension = true
            recomputePageOffsets()
            totalHeight = computeTotalHeight()
            restoreOffsetAfterReflow(oldOffsetY, oldTotalHeight, totalHeight, anchor)
            checkTranslationBounds()
        }

        dispatchPageChanged()
        maybeDispatchLoadingFinished()
        invalidate()
    }

    private fun recycleFarBitmaps(viewportTop: Float, viewportBottom: Float) {
        val keepMargin = (height / max(currentScale, 1f)) * KEEP_SCREEN_MULTIPLIER
        val keepTop = viewportTop - keepMargin
        val keepBottom = viewportBottom + keepMargin
        val currentPage = getCurrentPageIndex()
        val keepPageStart = max(0, currentPage - KEEP_PAGE_RADIUS)
        val keepPageEnd = min(pageMetrics.size - 1, currentPage + KEEP_PAGE_RADIUS)

        for (index in pageMetrics.indices) {
            val metric = pageMetrics[index]
            val pageBottom = metric.startY + metric.getDisplayHeight(width)
            val outsidePageWindow = index < keepPageStart || index > keepPageEnd
            val outsideViewportWindow = pageBottom < keepTop || metric.startY > keepBottom
            if ((outsidePageWindow || outsideViewportWindow) && metric.bitmap != null) {
                metric.bitmap?.recycle()
                metric.bitmap = null
            }
        }
    }

    private fun recomputePageOffsets() {
        var currentY = 0f
        val viewWidth = max(width, 1080)
        for (metric in pageMetrics) {
            metric.startY = currentY
            currentY += metric.getDisplayHeight(viewWidth)
        }
    }

    private fun computeTotalHeight(): Float {
        var sum = 0f
        val viewWidth = max(width, 1080)
        for (metric in pageMetrics) {
            sum += metric.getDisplayHeight(viewWidth)
        }
        return sum
    }

    private fun applyInitialPosition(initialPage: Int) {
        imageMatrix.reset()
        currentScale = 1.0f
        if (initialPage in pageMetrics.indices) {
            imageMatrix.postTranslate(0f, -pageMetrics[initialPage].startY)
        }
        checkTranslationBounds()
    }

    private fun getCurrentUnscaledOffsetY(): Float {
        val values = FloatArray(9)
        imageMatrix.getValues(values)
        return -values[Matrix.MTRANS_Y] / max(currentScale, 0.0001f)
    }

    private fun captureViewportAnchor(unscaledOffsetY: Float): ViewportAnchor? {
        if (pageMetrics.isEmpty()) return null
        var anchorIndex = 0
        for (index in pageMetrics.indices) {
            if (pageMetrics[index].startY <= unscaledOffsetY) {
                anchorIndex = index
            } else {
                break
            }
        }
        anchorIndex = max(0, min(anchorIndex, pageMetrics.size - 1))
        val metric = pageMetrics[anchorIndex]
        val pageHeight = max(1f, metric.getDisplayHeight(max(width, 1080)))
        val offsetInPage = max(0f, min(unscaledOffsetY - metric.startY, pageHeight))
        val ratio = max(0f, min(offsetInPage / pageHeight, 1f))
        return ViewportAnchor(anchorIndex, ratio)
    }

    private fun restoreOffsetAfterReflow(
        oldOffsetY: Float,
        oldTotalHeight: Float,
        newTotalHeight: Float,
        anchor: ViewportAnchor?
    ) {
        val values = FloatArray(9)
        imageMatrix.getValues(values)
        val transX = values[Matrix.MTRANS_X]

        val anchorOffsetY = if (anchor != null && pageMetrics.isNotEmpty()) {
            val index = max(0, min(anchor.pageIndex, pageMetrics.size - 1))
            val metric = pageMetrics[index]
            val pageHeight = max(1f, metric.getDisplayHeight(max(width, 1080)))
            metric.startY + pageHeight * anchor.pageOffsetRatio
        } else if (oldTotalHeight > 0f) {
            max(0f, min(oldOffsetY / oldTotalHeight, 1f)) * newTotalHeight
        } else 0f

        imageMatrix.setTranslate(transX, -anchorOffsetY * currentScale)
    }

    private fun getUnscaledViewport(): Viewport {
        val inverse = Matrix()
        imageMatrix.invert(inverse)
        val points = floatArrayOf(0f, 0f, width.toFloat(), height.toFloat())
        inverse.mapPoints(points)
        val top = min(points[1], points[3])
        val bottom = max(points[1], points[3])
        return Viewport(top, bottom)
    }

    private fun checkTranslationBounds() {
        if (pageMetrics.isEmpty() || width <= 0 || height <= 0) return

        val values = FloatArray(9)
        imageMatrix.getValues(values)
        var transX = values[Matrix.MTRANS_X]
        var transY = values[Matrix.MTRANS_Y]

        val scaledWidth = width * currentScale
        transX = if (scaledWidth > width) {
            val dxMin = width - scaledWidth
            max(min(transX, 0f), dxMin)
        } else {
            (width - scaledWidth) / 2f
        }

        val scaledTotalHeight = totalHeight * currentScale
        if (scaledTotalHeight > height) {
            val dyMin = height - scaledTotalHeight
            if (transY > 0f) {
                transY = 0f
                onEdgeListener?.onReachTop()
            } else if (transY < dyMin) {
                transY = dyMin
                onEdgeListener?.onReachBottom()
            }
        } else {
            transY = (height - scaledTotalHeight) / 2f
        }

        imageMatrix.setValues(floatArrayOf(
            currentScale, 0f, transX,
            0f, currentScale, transY,
            0f, 0f, 1f
        ))
    }

    private fun checkScaleBounds(focusX: Float, focusY: Float) {
        if (currentScale < 1.0f) {
            val factor = 1.0f / max(currentScale, 0.0001f)
            imageMatrix.postScale(factor, factor, focusX, focusY)
            currentScale = 1.0f
        } else if (currentScale > MAX_SCALE) {
            val factor = MAX_SCALE / currentScale
            imageMatrix.postScale(factor, factor, focusX, focusY)
            currentScale = MAX_SCALE
        }
    }

    private fun recycleAllBitmaps() {
        for (metric in pageMetrics) {
            metric.bitmap?.recycle()
            metric.bitmap = null
            metric.isLoading = false
            metric.isFailed = false
        }
    }

    private fun dispatchPageChanged() {
        val newPage = max(0, getCurrentPageIndex()) + 1
        if (newPage != lastDispatchedPage) {
            lastDispatchedPage = newPage
            onPageChangeListener?.onPageChange(newPage, pageMetrics.size)
        }
    }

    private fun dispatchTransformChanged() {
        onTransformChangeListener?.onTransformChange()
    }

    private fun dispatchLoadingChanged(isLoading: Boolean) {
        onLoadingChangeListener?.onLoadingChange(isLoading)
    }

    private fun maybeDispatchLoadingFinished() {
        for (metric in pageMetrics) {
            if (metric.isLoading) return
        }
        dispatchLoadingChanged(false)
    }

    private class PageMetric(
        val pageIndex: Int,
        var originalWidth: Int,
        var originalHeight: Int
    ) {
        var startY: Float = 0f
        var hasRealDimension: Boolean = false
        var bitmap: Bitmap? = null
        var isLoading: Boolean = false
        var isFailed: Boolean = false
        var retryCount: Int = 0

        init {
            originalWidth = max(1, originalWidth)
            originalHeight = max(1, originalHeight)
        }

        fun getDisplayHeight(viewWidth: Int): Float {
            val safeWidth = max(1, originalWidth)
            val safeHeight = max(1, originalHeight)
            return viewWidth.toFloat() / safeWidth.toFloat() * safeHeight.toFloat()
        }
    }

    private class PageLoadTarget(val index: Int, val metric: PageMetric)
    private class Viewport(val top: Float, val bottom: Float)
    private class ViewportAnchor(val pageIndex: Int, val pageOffsetRatio: Float)
    private class BitmapLoadResult(val bitmap: Bitmap?, val originalWidth: Int, val originalHeight: Int)

    private inner class ScaleListener : ScaleGestureDetector.SimpleOnScaleGestureListener() {
        override fun onScale(detector: ScaleGestureDetector): Boolean {
            val factor = detector.scaleFactor
            imageMatrix.postScale(factor, factor, detector.focusX, detector.focusY)
            currentScale *= factor
            checkScaleBounds(detector.focusX, detector.focusY)
            checkTranslationBounds()
            dispatchTransformChanged()
            invalidate()
            return true
        }
    }

    private inner class GestureListener : GestureDetector.SimpleOnGestureListener() {
        override fun onDown(e: MotionEvent): Boolean {
            return true
        }

        override fun onScroll(e1: MotionEvent?, e2: MotionEvent, distanceX: Float, distanceY: Float): Boolean {
            imageMatrix.postTranslate(-distanceX, -distanceY)
            checkTranslationBounds()
            dispatchPageChanged()
            dispatchTransformChanged()
            invalidate()
            return true
        }

        override fun onFling(e1: MotionEvent?, e2: MotionEvent, velocityX: Float, velocityY: Float): Boolean {
            val values = FloatArray(9)
            imageMatrix.getValues(values)
            val startY = values[Matrix.MTRANS_Y].roundToInt()
            val minScrollY = (height - totalHeight * currentScale).roundToInt()
            val maxScrollY = 0
            scroller.fling(0, startY, 0, velocityY.roundToInt(), 0, 0, min(0, minScrollY), maxScrollY)
            postInvalidateOnAnimation()
            return true
        }

        override fun onSingleTapConfirmed(e: MotionEvent): Boolean {
            val page = findPageAtScreenY(e.y)
            if (page in pageMetrics.indices && pageMetrics[page].isFailed) {
                pageMetrics[page].retryCount = 0
                reloadPage(page)
                return true
            }
            performClick()
            return true
        }

        override fun onDoubleTap(e: MotionEvent): Boolean {
            // 双击智能放大/还原
            if (currentScale > 1.05f) {
                // 还原为 1.0x
                val factor = 1.0f / currentScale
                imageMatrix.postScale(factor, factor, e.x, e.y)
                currentScale = 1.0f
            } else {
                // 放大至 2.2x
                val factor = 2.2f / currentScale
                imageMatrix.postScale(factor, factor, e.x, e.y)
                currentScale = 2.2f
            }
            checkScaleBounds(e.x, e.y)
            checkTranslationBounds()
            dispatchTransformChanged()
            invalidate()
            return true
        }
    }
}
