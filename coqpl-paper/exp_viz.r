library(functional)
library(ggplot2)
library(tikzDevice)

tikz('exp_viz.tex', standAlone = FALSE, width = 5,height = 5)
## bottom, left, top, and right.
par(mar = c(1,2,1,1))

xrang <- c(0,4)
yrang <- c(-5,5)

## exponentials
e  <- function(x) { 5*exp(-x) }
ne <- function(x) { -5*exp(-x) }

## func 1 + setup
curve(e,                                # the func
      n=30,                             # no of points eval'ed
      xlim=xrang, ylim=yrang,
      bty='l',                          # what does this do???
      xlab="time", ylab="",                 # axis labels
      axes=F,                           # draw axes separately
      xaxs="i", yaxs="i",
      col="red",
      )

axis(1,                                 # x axis
     pos=0,                             # at y=0
     at=xrang,                          # where to put labels (+ extend the line)
     labels=F,                          # don't show x axis
     tck=0,
     xaxs="i", yaxs="i",
     )

axis(2,                                 # y axis
     pos=0,                             # at x=0
     at=c(-4,0,4),
     lab=c("",0,""),
     tck=0,
     )



## neg
curve(ne,
      add=TRUE,
      col="red",
      )


## Draw some random points
set.seed(114)

startT <- 0.1
startX <- 2.5

# vals of e and ne at time t
getBounds <- function(t) { list(u = e(t), l = ne(t)) }

#ctrlRuns <- runif(4, 0,4)
ctrlRuns <- c(1.260825, 0.587869, 3.509754, 2.328480)
ctrlBounds <- lapply(ctrlRuns, getBounds)

set.seed(123)
pickRand <- function(ls) { runif(1,ls$l,ls$u) }
ctrlRunVals <- lapply(ctrlBounds, pickRand)


xs <- append(ctrlRuns, startT)
ys <- unlist(append(ctrlRunVals,startX))

# "zip" and sort so the lines connect properly
data <- data.frame(x = xs, y = ys)
data <- data[order(data$x), ]

# draw lines
lines(data, bty="n")
points(xs,ys,pch=4, bty="n")


# close tikz generation
dev.off()
