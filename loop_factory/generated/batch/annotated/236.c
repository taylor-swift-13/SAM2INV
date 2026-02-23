int main1(int k,int q){
  int h, j, t;

  h=64;
  j=0;
  t=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 64 && j <= h && (t == 0 || t == 64) && t % 8 == 0;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant j >= 0;
  loop invariant 0 <= j;
  loop invariant j <= h;
  loop invariant t % 8 == 0;
  loop invariant h == 64;
  loop invariant (k == \at(k, Pre));
  loop invariant (q == \at(q, Pre));
  loop invariant (j > 0) ==> t == 0;
  loop invariant 0 <= j <= h;
  loop invariant (j >= 1) ==> t == 0;
  loop assigns t, j;
*/
while (j<=h-1) {
      t = t*2;
      t = t%8;
      j = j+1;
  }

}
