int main1(int b,int k){
  int v, o, t, d;

  v=b+23;
  o=0;
  t=k;
  d=o;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == b + 23;
  loop invariant o >= 0;
  loop invariant k == \at(k, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant (o == 0) ==> (t == k);
  loop invariant (o > 0) ==> (t % 3 == 0);
  loop invariant v == \at(b, Pre) + 23;

  loop assigns o, t;
*/
while (1) {
      t = t*3+3;
      o = o+1;
  }

}
