int main1(){
  int olje, g, n4, gy, i0b, f;

  olje=1*2;
  g=(1%60)+60;
  n4=(1%9)+2;
  gy=0;
  i0b=0;
  f=olje;

  while (1) {
      if (g<=n4*gy+i0b) {
          break;
      }
      if (i0b==n4-1) {
          i0b = 0;
          gy += 1;
      }
      else {
          i0b += 1;
      }
      f = (gy)+(f);
  }

}
