int main1(){
  int sqvr, o9, kd, eot, g9j;

  sqvr=1+8;
  o9=0;
  kd=-6;
  eot=0;
  g9j=0;

  while (1) {
      if (!(o9 < sqvr)) {
          break;
      }
      eot = (eot + kd < g9j ? eot + kd : (o9++, eot + kd - g9j));
      g9j += o9;
      o9 = sqvr;
  }

}
