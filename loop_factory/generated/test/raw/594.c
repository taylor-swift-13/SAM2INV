int main1(int r){
  int jidk, lc, uds;

  jidk=0;
  lc=(r%20)+10;
  uds=(r%15)+8;

  while (lc>0&&uds>0) {
      if (jidk%2==0) {
          lc--;
      }
      else {
          uds = uds - 1;
      }
      jidk++;
  }

}
