int main1(){
  int z9v, um, tn;

  z9v=(1%23)+18;
  um=3;
  tn=0;

  while (um<z9v) {
      if (um%2==0) {
          if (tn>0) {
              tn -= 1;
              tn++;
          }
      }
      else {
          if (tn>0) {
              tn -= 1;
              tn++;
          }
      }
      um++;
      tn++;
  }

}
