module Shapes

export
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

export
triangle : Double -> Double -> Shape
triangle = Triangle

export
rectangle : Double -> Double -> Shape
rectangle = Rectangle

export
circle : Double -> Shape
circle = Circle

public export
data ShapeView : (shape : Shape) -> Type where
  STriangle : ShapeView (triangle base height)
  SRectangle : ShapeView (rectangle width height)
  SCircle : ShapeView (circle radius)
  
export
shapeView : (shape : Shape) -> ShapeView shape
shapeView (Triangle base height) = STriangle 
shapeView (Rectangle width height) = SRectangle
shapeView (Circle radius) = SCircle

