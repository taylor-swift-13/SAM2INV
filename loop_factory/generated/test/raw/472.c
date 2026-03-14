int main1(int y){
  int hr, s5, p7f, di, c2;

  hr=(y%31)+17;
  s5=0;
  p7f=(y%18)+5;
  di=(y%15)+3;
  c2=p7f;

  while (1) {
      if (!(p7f!=0)) {
          break;
      }
      di -= 1;
      p7f = p7f - 1;
      c2 += s5;
  }

  while (1) {
      if (!(p7f+1<=hr)) {
          break;
      }
      di = di+y+y;
      di++;
      p7f += 1;
  }

}
