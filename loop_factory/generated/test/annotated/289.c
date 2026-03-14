int main1(){
  int k9ti, kmpg, w, b, d9, o5;
  k9ti=1+17;
  kmpg=1;
  w=k9ti;
  b=kmpg;
  d9=k9ti;
  o5=k9ti;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == k9ti;
  loop invariant d9 == k9ti;
  loop invariant b == 1;
  loop invariant (kmpg - 1) % 6 == 0;
  loop invariant o5 == k9ti || o5 == w + b + d9;
  loop invariant o5 <= w + b + d9;
  loop assigns kmpg, o5;
*/
for (; kmpg<=k9ti-1; kmpg += 6) {
      o5 = w+b+d9;
  }
}