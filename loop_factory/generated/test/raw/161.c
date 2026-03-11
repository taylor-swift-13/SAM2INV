int main1(){
  int ivfb, k, hy4l, zw, yhs;

  ivfb=185;
  k=0;
  hy4l=23;
  zw=1;
  yhs=0;

  while (hy4l>0&&zw<=ivfb) {
      if (hy4l>zw) {
          hy4l = hy4l - zw;
      }
      else {
          hy4l = 0;
      }
      zw++;
      k += 1;
      yhs++;
  }

}
