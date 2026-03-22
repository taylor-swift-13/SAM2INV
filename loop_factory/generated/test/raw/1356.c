int main1(){
  int plq, z, att, w26, u1;

  plq=0;
  z=(1%20)+1;
  att=(1%25)+1;
  w26=0;
  u1=plq;

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
