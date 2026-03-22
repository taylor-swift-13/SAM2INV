int main1(){
  int qrs, ys, p3, iqy, epg;

  qrs=1;
  ys=qrs;
  p3=0;
  iqy=0;
  epg=qrs;

  while (1) {
      if (!(iqy<qrs)) {
          break;
      }
      iqy = iqy + 1;
      p3++;
      epg = epg + p3;
      epg += ys;
  }

  while (1) {
      if (!(epg*4<=p3)) {
          break;
      }
      qrs += epg;
      iqy = iqy+ys*epg;
      ys = ys*3;
      p3 = (epg*4)-1;
  }

}
