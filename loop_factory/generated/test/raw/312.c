int main1(int j,int l){
  int okl2, eg, dx;

  okl2=13;
  eg=okl2;
  dx=2;

  while (eg>2) {
      if (dx==1) {
          dx = 2;
      }
      else {
          if (dx==2) {
              dx = 1;
          }
      }
      l += dx;
      j++;
  }

}
