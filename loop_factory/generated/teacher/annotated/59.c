int main1(int a,int b){
  int e, l, v, j;

  e=a;
  l=0;
  v=b;
  j=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l >= 0;

  loop invariant a == \at(a, Pre) && 0 <= l;
  loop invariant (0 <= l && e > 0) ==> (l <= e) && (j * a >= 0);
  loop invariant e == a;
  loop invariant 0 <= l;
  loop invariant e == \at(a, Pre);
  loop invariant a == \at(a, Pre);
  loop assigns l, j;
*/
while (l<e) {
      j = j+j;
      l = l+1;
  }

}
