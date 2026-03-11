int main1(int b,int q){
  int h, r, j, w;

  h=q+19;
  r=h;
  j=0;
  w=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w >= -5 && w <= -5 + 2*j && q == \at(q, Pre) && b == \at(b, Pre);
  loop invariant h == q + 19;
  loop invariant j >= 0;

  loop invariant j < h/2 ==> w == -5;

  loop invariant q == \at(q, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant (j <= h/2) ==> w == -5;

  loop invariant h == \at(q, Pre) + 19;
  loop invariant 0 <= j;
  loop invariant h >= 0 ==> j <= h;
  loop invariant w >= -5 && (w + 5) % 2 == 0;

  loop invariant (w + 5) % 2 == 0;
  loop invariant w >= -5 && w <= -5 + 2*j;
  loop invariant (j < h/2) ==> (w == -5) && (j >= h/2) ==> (w == -5 + 2*(j - h/2));
  loop invariant (j <= h/2) ==> (w == -5);


  loop invariant w >= -5;
  loop invariant w <= -5 + 2*j;
  loop invariant (j <= h) || (h <= 0);
  loop invariant (j < h/2) ==> (w == -5);

  loop assigns j, w;
*/
while (j<h) {
      if (j>=h/2) {
          w = w+2;
      }
      j = j+1;
  }
/*@
  assert !(j<h) &&
         (w >= -5 && w <= -5 + 2*j && q == \at(q, Pre) && b == \at(b, Pre));
*/


}
