int main1(int i){
  int ri, s, c, j, id;

  ri=(i%13)+10;
  s=0;
  c=0;
  j=-5;
  id=ri;

  while (1) {
      c = c + 1;
      j = j + c;
      j = id+(-1);
      id = id + 3;
      id = id + i;
      s++;
      if (s>=ri) {
          break;
      }
  }

  while (id<j) {
      s++;
      c = c + s;
      id++;
  }

}
