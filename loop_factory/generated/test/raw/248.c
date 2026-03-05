int main1(int n){
  int nr, d;

  nr=45;
  d=0;

  while (d<nr) {
      if (d<nr/2) {
          d++;
      }
      else {
          d -= 1;
      }
      d++;
      n += d;
  }

}
