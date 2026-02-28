int main1(int k,int q){
  int i, v, a, t;

  i=(k%6)+8;
  v=0;
  a=2;
  t=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant a == 2*(v+1);
  loop invariant 0 <= v;
  loop invariant v <= i;
  loop invariant (v > 0) ==> (t % 2 == 0);
  loop invariant i >= 3;
  loop invariant i <= 13;
  loop invariant i == (k % 6) + 8;
  loop invariant a == 2 + 2*v;
  loop invariant i == (\at(k,Pre) % 6) + 8;
  loop invariant i == k % 6 + 8;
  loop invariant 0 <= v <= i;
  loop assigns a, t, v;
*/
while (v<=i-1) {
      a = a+2;
      t = t+a;
      t = t+t;
      v = v+1;
  }

}
