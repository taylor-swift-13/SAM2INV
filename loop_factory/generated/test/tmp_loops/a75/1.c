int main1(int t){
  int e9a2, ovr, wks, rw15, ah, f, qds5, l25;

  e9a2=t;
  ovr=e9a2;
  wks=48;
  rw15=0;
  ah=1;
  f=0;
  qds5=ovr;
  l25=ovr;

  while (1) {
      if (!(wks>0&&ovr<e9a2)) {
          break;
      }
      f = ah;
      if (wks>=ah) {
          wks = wks - ah;
          rw15 = rw15 + ah;
      }
      else {
          rw15 = rw15 + wks;
          wks = 0;
      }
      ah = ah + 1;
      ovr++;
      if (ovr+1<=f+e9a2) {
          l25++;
      }
      qds5 = qds5 + rw15;
      t = t + rw15;
      l25 += t;
  }

}
