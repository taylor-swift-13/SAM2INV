int main1(int a,int p){
  int b, j, x, v;

  b=43;
  j=b+4;
  x=a;
  v=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == 43;
  loop invariant a == \at(a, Pre) && p == \at(p, Pre) && j >= 0;
  loop invariant j >= 0;
  loop invariant j <= b + 4;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant j <= 47;
  loop invariant 0 <= j;
  loop invariant b == 43 && j >= 0 && j <= b + 4;
  loop invariant a == \at(a, Pre) && p == \at(p, Pre);
  loop assigns j;
*/
while (j>0) {
      j = j/2;
  }

}
