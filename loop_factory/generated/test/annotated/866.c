int main1(int v,int b){
  int g8, kp, egt, m9;
  g8=51;
  kp=g8;
  egt=0;
  m9=v+1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m9 == \at(v, Pre) + kp - 50;
  loop invariant kp >= 51;
  loop invariant m9 == v + kp - 50;
  loop invariant m9 >= v + 1;
  loop invariant egt >= 0;
  loop invariant (egt <= m9*m9);
  loop assigns m9, egt, kp;
*/
while (kp-1>=0) {
      m9++;
      egt = m9*m9;
      kp = kp + 1;
  }
}