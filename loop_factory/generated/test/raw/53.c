int main1(){
  int vrts, ynk, hs, su;

  vrts=(1%29)+6;
  ynk=0;
  hs=0;
  su=4;

  while (1) {
      if (!(ynk<vrts&&su>0)) {
          break;
      }
      ynk += 1;
      hs += su;
      hs = hs + hs;
      su -= 1;
  }

}
