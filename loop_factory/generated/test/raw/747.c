int main1(){
  int r3, n9z, vbx, by3, r;

  r3=(1%60)+60;
  n9z=(1%9)+2;
  vbx=0;
  by3=0;
  r=-6;

  while (r3>n9z*vbx+by3) {
      if (by3==n9z-1) {
          by3 = 0;
          vbx = vbx + 1;
      }
      else {
          by3 = by3 + 1;
      }
      r = r+(vbx%8);
  }

}
