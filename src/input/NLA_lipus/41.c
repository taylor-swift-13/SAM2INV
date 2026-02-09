/*@ requires X > 0 && Y > 0 && X >= Y;*/
int main1(){

  int X, Y, v, x, y;
  
  v = 2 * Y - X;
  y = 0;
  x = 0;

  while (x <= X) {
        if (v < 0) {
            v = v + 2 * Y;
        } else {
            v = v + 2 * (Y - X);
            y++;
        }
        x++;

    }
  /*@ assert 2*Y*x - 2*x*y - X + 2*Y - v + 2*y == 0;*/
}

