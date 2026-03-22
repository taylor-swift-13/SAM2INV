int main1(int r,int z){
  int w, l5, s, l3v, wz;

  w=(r%18)+9;
  l5=-6;
  s=w;
  l3v=-1;
  wz=3;

  while (wz<=w) {
      l5 = l5 + s;
      s = s + l3v;
      z = z + s;
      r = r*2;
      wz++;
      l3v += 6;
  }

}
