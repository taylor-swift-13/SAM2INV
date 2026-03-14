int main1(){
  int ue, m, b, ls, g9;

  ue=169;
  m=2;
  b=0;
  ls=0;
  g9=0;

  for (; m<=ue-1; m++) {
      g9++;
      ls++;
      if (ls>=2) {
          ls -= 2;
          b += 1;
      }
  }

}
