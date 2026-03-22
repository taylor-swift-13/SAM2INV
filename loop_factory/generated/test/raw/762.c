int main1(){
  int q9, ld2, x, pl3;

  q9=(1%28)+8;
  ld2=(1%22)+5;
  x=0;
  pl3=-3;

  while (ld2!=0) {
      if (ld2%2==1) {
          x += q9;
          ld2--;
      }
      q9 = 2*q9;
      ld2 = ld2/2;
      pl3 += x;
      pl3 = (pl3)+(pl3*pl3);
  }

}
