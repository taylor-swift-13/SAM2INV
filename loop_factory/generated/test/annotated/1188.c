int main1(){
  int qg, toyy, m, mg6, on;
  qg=1-1;
  toyy=(1%28)+8;
  m=(1%22)+5;
  mg6=0;
  on=qg;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant toyy % 9 == 0;
  loop invariant on % 36 == 0;
  loop invariant mg6 >= 0;
  loop invariant qg == 0;
  loop invariant on >= 0;
  loop invariant toyy >= 9;
  loop invariant mg6 % 9 == 0;
  loop invariant 0 <= m <= 6;
  loop assigns mg6, m, toyy, on;
*/
while (1) {
      if (!(m!=0)) {
          break;
      }
      if (m%2==1) {
          mg6 = mg6 + toyy;
          m -= 1;
      }
      m = m/2;
      toyy = 2*toyy;
      on = (toyy)+(on);
      on = on*2;
  }
}