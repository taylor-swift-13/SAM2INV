int main1(int a,int b,int k,int q){
  int x, t, p, v;

  x=76;
  t=0;
  p=0;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p >= 0;
  loop invariant (p == 0) ==> (v == a);
  loop invariant (p > 0) ==> (v == 77 - p);
  loop invariant x == 76;
  loop invariant (p > 0) ==> (v == x - p + 1);
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant (p == 0 ==> v == a);
  loop invariant (p >= 1 ==> v + p == x + 1);
  loop assigns p, v;
*/
while (1) {
      v = x-p;
      p = p+1;
  }

}
