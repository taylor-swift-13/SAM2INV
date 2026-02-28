int main1(int m,int q){
  int c, x, b, v, g;

  c=60;
  x=0;
  b=q;
  v=-6;
  g=c;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant b == q + 2*(x/5);
  loop invariant x <= c;
  loop invariant x % 5 == 0;
  loop invariant c == 60;
  loop invariant 2*x == 5*(b - q);
  loop invariant x >= 0;
  loop invariant b >= q;
  loop invariant 5*b - 2*x == 5*q;
  loop invariant v == -6 + ((b - q)/2)*q + ((b - q)/2)*(((b - q)/2) + 1);
  loop invariant 0 <= x;
  loop invariant 5*(b - q) == 2*x;
  loop invariant x*x + 5*x + 5*q*x - 25*v - 150 == 0;
  loop invariant v == (x/5)*q + (x/5)*((x/5)+1) - 6;
  loop assigns b, v, x;
*/
while (x<c) {
      b = b+2;
      v = v+b;
      x = x+5;
  }

}
