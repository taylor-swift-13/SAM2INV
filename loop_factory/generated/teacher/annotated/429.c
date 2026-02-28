int main1(int a,int q){
  int b, p, i;

  b=23;
  p=b;
  i=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant p >= 0;
  loop invariant p <= 23;
  loop invariant (p == 23) ==> (i == q);
  loop invariant b == 23;
  loop assigns i, p;
*/
while (p>=1) {
      i = i*i;
      p = p-1;
  }

}
