int main1(){
  int q7, yz, s, xxd;

  q7=80;
  yz=0;
  s=0;
  xxd=10;

  while (1) {
      if (!(s<=q7-1)) {
          break;
      }
      if (s<q7/2) {
          s += 2;
      }
      else {
          s++;
      }
      xxd = xxd + yz;
      xxd += 6;
  }

}
