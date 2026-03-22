int main1(int f,int j){
  int a, olh, rj, s, scts, ob2, txcp, e4;

  a=j*5;
  olh=a;
  rj=1;
  s=1;
  scts=1;
  ob2=1;
  txcp=j;
  e4=j;

  while (1) {
      if (!(scts<=a)) {
          break;
      }
      rj = rj*(f/scts);
      if ((scts/2)%2==0) {
          ob2 = 1;
      }
      else {
          ob2 = -1;
      }
      s = s+ob2*rj;
      scts++;
      rj = rj*(f/scts);
      if ((olh%7)==0) {
          j = j*j+txcp;
      }
      f = f + ob2;
      txcp += rj;
      txcp = txcp*4+3;
      e4 = e4*txcp+3;
  }

}
