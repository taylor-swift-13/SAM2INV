int main1(int k,int m){
  int g, i, v;

  g=(k%14)+12;
  i=0;
  v=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 0;
  loop invariant k == \at(k,Pre);
  loop invariant m == \at(m,Pre);
  loop invariant g == (\at(k,Pre) % 14) + 12;
  loop invariant v >= -3;
  loop invariant (4 <= k+g) ==> (v <= 6);
  loop invariant g == (k % 14) + 12;

  loop invariant g == ((\at(k, Pre) % 14) + 12);
  loop invariant (4 <= k+g) ==> v <= 6;
  loop assigns v;
*/
while (1) {
      v = v+4;
      if (i+4<=k+g) {
          v = v%7;
      }
  }

}
