int main1(int l,int r){
  int k93, kr, j;

  k93=r;
  kr=0;
  j=3;

  while (kr<k93) {
      if (kr>=k93/2) {
          j += 2;
      }
      kr += 1;
      l = l + kr;
  }

}
