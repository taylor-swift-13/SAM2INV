int main1(int m){
  int x3, fkr, r75, hw8, b2, z;

  x3=m*4;
  fkr=0;
  r75=0;
  hw8=0;
  b2=0;
  z=0;

  while (fkr<x3) {
      if (fkr%7==0) {
          z += 1;
      }
      else {
          if (fkr%6==0) {
              b2++;
          }
          else {
              if (fkr%4==0) {
                  hw8 = hw8 + 1;
              }
              else {
                  r75 = r75 + 1;
              }
          }
      }
      fkr += 1;
      m = (m+b2)%5;
  }

}
