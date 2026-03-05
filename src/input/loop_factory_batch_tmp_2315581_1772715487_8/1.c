int main1(int q,int e){
  int lk, c, j;

  lk=e*5;
  c=lk;
  j=3;

  while (c<=lk-1) {
      j = c%5;
      if (c>=j) {
          j = (c-j)%5;
          j = j+j-j;
      }
      else {
          j += j;
      }
      c = c + 1;
      e = e+(c%2);
  }

}
