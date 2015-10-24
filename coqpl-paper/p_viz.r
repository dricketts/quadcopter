library(functional)
library(ggplot2)
library(tikzDevice)

tikz('p_viz.tex', standAlone = FALSE, width = 5,height = 5)
## bottom, left, top, and right.
par(mar = c(4,2,1,1))
par(family="serif")

xrang <- c(0,4)
yrang <- c(0,5)

## exponentials
e  <- function(x) { 5*exp(-x)  }
ne <- function(x) { -5*exp(-x) }

## func 1 + setup
curve(e,                                # the func
      n=30,                             # no of points eval'ed
      xlim=xrang, ylim=yrang,
      bty='l',                          # what does this do???
      xlab="time", ylab="x",                 # axis labels
#      axes=F,                           # draw axes separately
      xaxs="i", yaxs="i",
      yaxt='n',
      col="red",
      )

text(1,3, expression( italic(x == - alpha * e^{t - t[0]})), cex=1.3)

axis(1,                                 # x axis
     pos=0,                             # at y=0
     at=xrang,                          # where to put labels (+ extend the line)
     labels=F,                          # don't show x axis
     tck=0,
     xaxs="i", yaxs="i",
#           labels=c("0"),
     )

## axis(2,                                 # y axis
##      pos=0,                             # at x=0
##      at=c(-4,0,4),
##      lab=c("",0,""),
##      tck=0,
##      )


## Draw some random points
startT <- 0.1
startX <- 3.4

runTs <- c(0.7, 1.3, 1.5, 2.8, 3.6)
runXs <- c(1.3, 1.0, 0.7, 0.2, 0.1)

xs <- append(runTs, startT)
ys <- unlist(append(runXs,startX))

# "zip" and sort so the lines connect properly
 data <- data.frame(x = xs, y = ys)
 data <- data[order(data$x), ]

# draw lines
lines(data, bty="n")

## draw points
text(c(startT+0.1),c(startX+0.1),
     expression(
         group("(",list(italic(t[0]), italic(x[0])), ")")
     ),
     cex=0.9)

points(xs,ys,pch=4, bty="n")      #unlabelled


# close tikz generation
dev.off()
