int main1(int c,int t){
  int gb, oo7, kg2, rn;

  gb=(c%18)+19;
  oo7=3;
  kg2=0;
  rn=0;

  while (oo7<gb) {
      kg2 += 1;
      rn += 1;
      if (rn>=7) {
          rn = rn - 7;
          kg2 += 1;
      }
      oo7++;
  }

}
