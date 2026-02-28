int main1(int m,int n){
  int i, g, p, y;

  i=20;
  g=i;
  p=g;
  y=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 3*p + 4*g == 140;
  loop invariant i == 20;
  loop invariant (p - 20) % 4 == 0;
  loop invariant (g - 20) % 3 == 0;
  loop invariant g <= 20;
  loop invariant p >= 20;
  loop invariant 3*(p - 20) == 4*(20 - g);
  loop invariant g >= 2;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant 4*g + 3*p == 140;
  loop invariant 20 <= p <= 44;
  loop invariant 8*(y - 1) == (p - 20)*(p - 20) + 44*(p - 20);
  loop assigns p, y, g;
*/
while (g>2) {
      p = p+4;
      y = y+p;
      g = g-3;
  }

}
