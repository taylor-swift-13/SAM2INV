int main1(int k,int n){
  int h, j, v, b;

  h=31;
  j=0;
  v=-5;
  b=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j % 2 == 0;
  loop invariant 0 <= j;
  loop invariant j <= h;
  loop invariant b == k;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant h == 31;

  loop invariant (j % 2 == 0);
  loop invariant (0 <= j);
  loop invariant (j <= h);

  loop invariant (j == 0) ==> (v == -5);
  loop assigns v, j;
*/
while (j<=h-2) {
      v = v+b+b;
      v = v+1;
      if ((j%8)==0) {
          v = v+b;
      }
      j = j+2;
  }

}
