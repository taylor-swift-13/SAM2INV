int main1(int k,int q){
  int h, j, t;

  h=64;
  j=0;
  t=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 0;
  loop invariant h == 64;
  loop invariant t == h || t == h + 3;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant t <= h + 3;
  loop invariant t >= h;
  loop invariant 0 <= j;
  loop invariant j <= h;
  loop invariant k == \at(k, Pre) && q == \at(q, Pre) && (t == h || t == h+3);
  loop assigns t;
*/
while (j<=h-1) {
      t = t+2;
      t = h-(-3);
  }

}
