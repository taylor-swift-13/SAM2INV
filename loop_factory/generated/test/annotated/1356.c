int main1(){
  int plq, z, att, w26, u1;
  plq=0;
  z=(1%20)+1;
  att=(1%25)+1;
  w26=0;
  u1=plq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u1 == 2*z - 4;
  loop invariant 0 <= att;
  loop invariant att <= 2;
  loop invariant z >= 2;
  loop invariant z % 2 == 0;
  loop invariant u1 >= w26;
  loop invariant plq == 0;
  loop assigns w26, att, z, u1;
*/
while (1) {
      if (!(att!=0)) {
          break;
      }
      if (att%2==1) {
          w26 += z;
          att = att - 1;
      }
      else {
      }
      z = 2*z;
      att = att/2;
      u1 = (z)+(u1);
  }
}