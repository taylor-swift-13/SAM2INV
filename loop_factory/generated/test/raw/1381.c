int main1(){
  int yt, dzcb, h, j92, d4m, e, vq;

  yt=(1%35)+15;
  dzcb=(1%35)+15;
  h=1;
  j92=0;
  d4m=0;
  e=1;
  vq=-8;

  while (yt!=dzcb) {
      if (yt>dzcb) {
          yt = yt - dzcb;
          h = h - j92;
          d4m = d4m - e;
      }
      else {
          dzcb = dzcb - yt;
          j92 -= h;
          e = e - d4m;
      }
      vq = vq + d4m;
  }

}
