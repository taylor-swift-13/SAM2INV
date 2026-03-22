int main1(int l){
  int kf, vr, i8, f;

  kf=0;
  vr=0;
  i8=0;
  f=(l%18)+5;

  while (f>0) {
      f--;
      kf = kf+l*l;
      i8 = i8+l*l;
      vr = vr+l*l;
      l = l + kf;
  }

  while (i8>vr) {
      i8 -= vr;
      vr++;
      l += vr;
      f += l;
  }

}
