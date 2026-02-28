int main1(int m,int p){
  int u, s, v;

  u=48;
  s=3;
  v=s;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s >= 3;
  loop invariant (v == 0) || (v == 3);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant u == 48;
  loop invariant u == 48 && (v == 0 || v == 3) && s >= 3;
  loop invariant v >= 0;
  loop invariant v <= s;
  loop assigns s, v;
*/
while (1) {
      v = v+v;
      v = v-v;
      s = s+1;
  }

}
