int main1(int u,int j){
  int o4d, kc, v, b;
  o4d=54;
  kc=0;
  v=o4d;
  b=j*4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= kc <= o4d;
  loop invariant v + kc == o4d;
  loop invariant b == j*4 + (kc*(kc+1))/2;
  loop invariant u == \at(u,Pre) + kc*o4d - ((kc*(kc+1))/2);
  loop invariant o4d == 54;
  loop invariant j == \at(j,Pre);
  loop assigns kc, v, u, b;
*/
while (kc<o4d&&v>0) {
      kc = (1)+(kc);
      v -= 1;
      u += v;
      b += kc;
  }
}