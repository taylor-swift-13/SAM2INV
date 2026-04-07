int main1(){
  int kd, t6, ud, vi;

  kd=1+8;
  t6=3;
  ud=0;
  vi=6;

  while (1) {
      if (t6<kd/2) {
          ud = ud + vi;
      }
      else {
          ud++;
      }
      vi += t6;
      t6 += 1;
      if (t6>=kd) {
          break;
      }
  }

}
