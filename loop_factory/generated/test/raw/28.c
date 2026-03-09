int main1(){
  int n5, vsl8, qbv8;

  n5=(1%20)+5;
  vsl8=(1%20)+5;
  qbv8=(1%20)+5;

  while (1) {
      if (!(n5>=1)) {
          break;
      }
      if (vsl8>0) {
          if (qbv8>0) {
              n5 -= 1;
              vsl8 -= 1;
              qbv8 -= 1;
          }
      }
      vsl8++;
  }

}
