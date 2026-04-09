int main1(int d){
  int ax6n, f7zu, r, cqc8, cv;

  ax6n=(d%23)+10;
  f7zu=0;
  r=0;
  cqc8=0;
  cv=ax6n;

  while (1) {
      if (!(f7zu < ax6n)) {
          break;
      }
      r += d;
      f7zu = f7zu + 1;
      cqc8 += r;
      cv = cv+(cqc8%3);
  }

}
