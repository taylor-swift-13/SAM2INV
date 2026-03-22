int main1(){
  int s9, i, o4, v0m, oj, kj, lmps, tu, ht;
  s9=1+7;
  i=0;
  o4=41;
  v0m=0;
  oj=1;
  kj=0;
  lmps=i;
  tu=i;
  ht=i;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= i;
  loop invariant i <= s9;
  loop invariant o4 + v0m == 41;
  loop invariant tu == 0;
  loop invariant ht == 0;
  loop invariant oj >= 1;
  loop invariant o4 >= 0;
  loop invariant v0m >= 0;
  loop invariant kj >= 0;
  loop invariant lmps >= 0;
  loop assigns kj, o4, v0m, oj, i, lmps, tu, ht;
*/
while (1) {
      if (!(o4>0&&i<s9)) {
          break;
      }
      if (o4<oj) {
          kj = o4;
      }
      else {
          kj = oj;
      }
      o4 = o4 - kj;
      v0m = v0m + kj;
      if (i%2==0) {
          oj += 2;
      }
      else {
          oj++;
      }
      i = i + 1;
      lmps = lmps + v0m;
      tu = tu*tu;
      lmps = lmps + i;
      ht = ht+lmps*tu;
  }
}