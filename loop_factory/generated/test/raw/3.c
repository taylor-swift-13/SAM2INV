int main1(int h,int t,int s){
  int jv3s, az, dw;

  jv3s=t+22;
  az=jv3s;
  dw=(t%20)+5;

  while (1) {
      if (!(dw>0)) {
          break;
      }
      dw--;
      h = h + az;
      t = t + s;
      s += h;
  }

}
