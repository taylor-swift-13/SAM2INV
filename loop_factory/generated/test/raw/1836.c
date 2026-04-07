int main1(int l){
  int dr, ck, f7, ol;

  dr=l*5;
  ck=1;
  f7=l;
  ol=l*2;

  while (ck<dr) {
      ol = ol + 1;
      f7 = ol*ol;
      l = l + f7;
      ck = dr;
  }

}
