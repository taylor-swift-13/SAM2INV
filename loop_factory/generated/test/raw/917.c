int main1(){
  int fe2y, t, p, p6, fjd;

  fe2y=1*5;
  t=0;
  p=0;
  p6=fe2y;
  fjd=3;

  while (1) {
      if (!(p<=fe2y-1)) {
          break;
      }
      p++;
      t = (t+1)%3;
      p6++;
      fjd += p;
  }

}
