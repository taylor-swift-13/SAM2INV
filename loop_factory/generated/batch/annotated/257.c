int main1(int k,int n){
  int h, j, v, b;

  h=31;
  j=0;
  v=-5;
  b=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == -5 + j*b;
  loop invariant b == k;
  loop invariant h == 31;
  loop invariant j >= 0;

  loop invariant j % 2 == 0;
  loop invariant j <= h;
  loop invariant b == \at(k, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant 0 <= j;
  loop invariant v - b*j == -5;
  loop assigns v, j;
*/
while (j<=h-2) {
      v = v+b+b;
      j = j+2;
  }

}
