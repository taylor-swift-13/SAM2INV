int main1(int c){
  int vo, j, s;

  vo=(c%32)+13;
  j=0;
  s=-8;

  while (j < vo) {
      c = c + s;
      j++;
      s = s + 3;
  }

}
