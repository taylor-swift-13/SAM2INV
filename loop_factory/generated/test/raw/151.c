int main1(){
  int zu, q6, ytz, zg;

  zu=(1%28)+18;
  q6=0;
  ytz=zu;
  zg=zu;

  while (1) {
      if (!(q6<zu)) {
          break;
      }
      if (!(!(q6<zu/2))) {
          ytz += 1;
      }
      else {
          ytz = ytz + zg;
      }
      q6 = zu;
  }

}
