int main1(int b,int q){
  int n, h, g, l, u, d;

  n=30;
  h=n;
  g=h;
  l=h;
  u=-2;
  d=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= g;
  loop invariant 0 <= l;
  loop invariant g <= n;
  loop invariant l <= n;
  loop invariant g + l > 0;
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant g >= 0;
  loop invariant l >= 0;
  loop invariant g <= 30;
  loop invariant l <= 30;
  loop invariant g % 30 == 0;
  loop invariant l % 30 == 0;
  loop invariant 0 <= g <= 30;
  loop invariant 0 <= l <= 30;
  loop invariant g + l <= 60;
  loop assigns g, l;
*/
while (g!=0&&l!=0) {
      if (g>l) {
          g = g-l;
      }
      else {
          l = l-g;
      }
  }

}
