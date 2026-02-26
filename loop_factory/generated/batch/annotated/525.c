int main1(int a,int k){
  int m, j, v;

  m=(a%19)+5;
  j=1;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a,Pre);
  loop invariant k == \at(k,Pre);
  loop invariant m == (\at(a,Pre) % 19) + 5;
  loop invariant v == m + (j-1)*j/2;
  loop invariant j >= 1;
  loop invariant m == (a % 19) + 5;
  loop assigns v, j;
*/
while (1) {
      v = v+j;
      j = j+1;
  }

}
