int main1(){
  int hq, ud, n, mi, iar1, e;

  hq=39;
  ud=0;
  n=8;
  mi=0;
  iar1=1;
  e=0;

  while (1) {
      if (!(n>0&&ud<hq)) {
          break;
      }
      if (n<=iar1) {
          e = n;
      }
      else {
          e = iar1;
      }
      iar1 += 1;
      n = n - e;
      ud++;
      mi = mi + e;
  }

}
